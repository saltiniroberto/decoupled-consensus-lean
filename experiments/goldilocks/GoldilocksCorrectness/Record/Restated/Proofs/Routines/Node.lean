module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FGStateDefs
public import GoldilocksCorrectness.Proofs.Routines.Node
import all Goldilocks.Node

@[expose] public section

/-!
# Node, over a model

The relations between two node states of `GoldilocksCorrectness/Proofs/Routines/Node.lean` that the
execution pages read, over a model `M`, each read through the record's node readers: `StampsAt`
(what the second holds beyond the first is stamped with its clock), `FinalizedFrom` (the second
holds the first's tree, and its finalized block is the first's or the finalized block of the chain
state of a block of its tree), `JustifiedFrom` (the second's justified block is the first's or the
justified block of a chain state), `TreeGrows` (the second holds the first's blocks, votes and
stamps, and its finalized block is the first's or a descendant of it); their `refl`, `trans`,
`of_frame` and `congr_left` lemmas, and two lemmas of the wake; and the initial node state's
`FinalizedFromChain`, from the facts of the initial state and of the genesis block's chain state;
and the initial wake time as the spec's `proposal_window_start C 0` (the page opens the spec's node
page, as a routine page may). The facts of the tick and of the receipt state these relations written
out (`F.tk.tick_step`, `F.tk.tick_finalizedFrom`, `F.tk.tick_justifiedFrom`, `F.rcv.receive_step`,
…). The page's other declarations read routines the record has no member for.

At the spec's model each relation is the landed one (the equations `goldilocks_…`, in the simp set
`record_goldilocks`). The recovery section at the end of the page states each landed theorem
again, as the landed statement (`type_of%`), and proves it from its record form at the spec's model
`Model.goldilocks` and its facts `goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (FinalizedFromChain)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The initial wake time -/

/-- The wake time of the initial node state, which the facts of the initial state write as a time,
`C.t_ 0 + C.Δ − 4 * C.Δ * (C.k + 1)`, is the spec's start of slot `0`'s proposal window,
`proposal_window_start C 0`, whose body the spec keeps to its page.

The variables:
- `C`: the parameters.

Read aloud: the initial wake time is the start of the first proposal window. -/
theorem proposal_window_start_zero_eq (C : Config) :
    C.t_ 0 + C.Δ - 4 * C.Δ * ((C.k : Time) + 1) = proposal_window_start C 0 := by
  unfold proposal_window_start
  rfl

/-! ## The relations -/

section

variable (M : GoldilocksModel V)

/-- `StampsAt M n n'`: every block of `n'`'s tree that is not in `n`'s tree, and every Goldfish
vote `n'` holds under a slot that `n` does not hold under that slot, is stamped `n'.t` in `n'`.

The variables:
- `M`: the model;
- `n`, `n'`: the two node states.

Read aloud: what `n'` holds beyond `n` is stamped with `n'`'s clock. -/
def StampsAt (n n' : M.N) : Prop :=
  (∀ B ∈ n'.tree, B ∉ n.tree → n'.blockStamp B = some (n'.t : Stamp)) ∧ ACStampsAt M n n' n'.t

/-- `FinalizedFrom M C n n'`: `n'`'s tree holds `n`'s, and `n'`'s finalized block is `n`'s or the
finalized block of the chain state `M.chainStateOf C B` of a block `B` of `n'`'s tree.

The variables:
- `M`: the model;
- `C`: the parameters; `n`, `n'`: the two node states.

Read aloud: `n'` holds `n`'s tree, and its finalized block is `n`'s or comes from a chain it
holds. -/
def FinalizedFrom (C : Config) (n n' : M.N) : Prop :=
  n.tree ⊆ n'.tree ∧
    (n'.finalized = n.finalized ∨ ∃ B ∈ n'.tree, n'.finalized = (M.chainStateOf C B).F)

/-- `JustifiedFrom M C n n'`: `n'`'s justified block is `n`'s, or the justified block of the chain
state `M.chainStateOf C D` of some block `D`.

The variables:
- `M`: the model;
- `C`: the parameters; `n`, `n'`: the two node states.

Read aloud: `n'`'s justified block is `n`'s or comes from a chain. -/
def JustifiedFrom (C : Config) (n n' : M.N) : Prop :=
  n'.justified = n.justified ∨ ∃ D : Block V, n'.justified = (M.chainStateOf C D).J

/-- `TreeGrows M n n'`: `n'`'s tree holds `n`'s; `n`'s finalized block is `n'`'s or an ancestor of
`n'`'s; for every slot, `n`'s Goldfish votes of that slot are a prefix of `n'`'s; every block of
`n`'s tree has the same stamp in `n'`; and every vote `n` holds under a slot has the same stamp in
`n'`.

The variables:
- `M`: the model;
- `n`, `n'`: the two node states.

Read aloud: `n'` holds every block and vote `n` holds, with the same stamps, and its finalized
block is `n`'s or a descendant of it. -/
def TreeGrows (n n' : M.N) : Prop :=
  n.tree ⊆ n'.tree ∧ n.finalized.AncestorEq n'.finalized ∧
    (∀ s : Slot, n.votesHeld s <+: n'.votesHeld s) ∧
    (∀ B ∈ n.tree, n'.blockStamp B = n.blockStamp B) ∧
    ∀ s : Slot, ∀ vote ∈ n.votesHeld s, n'.voteStamp vote = n.voteStamp vote

end

/-! ## Their lemmas -/

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- A node state holds nothing beyond itself.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state.

Read aloud: what a node state holds beyond itself is stamped, vacuously. -/
theorem StampsAt.refl (n : M.N) : StampsAt M n n :=
  ⟨fun _ hB hn => absurd hB hn, ACStampsAt.refl M F n n.t⟩

/-- `StampsAt` reads only the tree and the votes held of the node state it starts from: two node
states with the same tree and the same votes held have the same `StampsAt` relations to a third.

The variables:
- `M`: the model; `F`: its facts;
- `n₀`, `n`: the two node states with the same tree and votes held; `n'`: the third.

Read aloud: what `n'` holds beyond `n₀` is what it holds beyond `n`, when the two hold the same. -/
theorem StampsAt.congr_left {n₀ n n' : M.N} (hT : n₀.tree = n.tree)
    (hV : M.votesHeld n₀ = M.votesHeld n) (h : StampsAt M n₀ n') : StampsAt M n n' := by
  obtain ⟨hB, hA⟩ := h
  refine ⟨fun B hB' hn => hB B hB' (by rw [hT]; exact hn), fun s vote hv hn => hA s vote hv ?_⟩
  change vote ∉ M.votesHeld n₀ s
  rw [hV]
  exact hn

/-- A node state is related to itself by `FinalizedFrom`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `n`: the node state.

Read aloud: a node state holds its own tree and finalized block. -/
theorem finalizedFrom_refl (C : Config) (n : M.N) : FinalizedFrom M C n n :=
  ⟨Finset.Subset.refl _, Or.inl rfl⟩

/-- `FinalizedFrom` is transitive.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `n`, `n'`, `n''`: the three node states.

Read aloud: `FinalizedFrom` composes. -/
theorem finalizedFrom_trans (C : Config) {n n' n'' : M.N} (h : FinalizedFrom M C n n')
    (h' : FinalizedFrom M C n' n'') : FinalizedFrom M C n n'' := by
  obtain ⟨hT, hF⟩ := h
  obtain ⟨hT', hF'⟩ := h'
  refine ⟨hT.trans hT', ?_⟩
  rcases hF' with hF' | ⟨B, hB, hBF⟩
  · rcases hF with hF | ⟨B, hB, hBF⟩
    · exact Or.inl (hF'.trans hF)
    · exact Or.inr ⟨B, hT' hB, hF'.trans hBF⟩
  · exact Or.inr ⟨B, hB, hBF⟩

/-- Two node states with the same tree and the same finalized block are related by
`FinalizedFrom`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `n`, `n'`: the two node states.

Read aloud: a step that keeps the tree and the finalized block relates its input to its output. -/
theorem finalizedFrom_of_frame (C : Config) {n n' : M.N} (hT : n'.tree = n.tree)
    (hF : n'.finalized = n.finalized) : FinalizedFrom M C n n' :=
  ⟨by rw [hT], Or.inl hF⟩

/-- The initial node state satisfies `FinalizedFromChain`: its finalized block is the genesis
block, the finalized block of the genesis block's chain state.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `v`: the validator.

Read aloud: a node starts with the genesis block finalized, which the genesis block's chain
finalizes. -/
theorem initial_finalizedFromChain (C : Config) (v : V) :
    FinalizedFromChain M C (M.initial C v) := by
  refine ⟨Block.genesis, ?_, ?_⟩
  · rw [F.init.initial_tree C v]
    exact Finset.mem_singleton_self _
  · rw [F.init.initial_finalized C v, (F.cs.cs_initial_eq C).2.2.2.2.2.2.2.2.2.2.1]

/-- A node state is related to itself by `JustifiedFrom`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `n`: the node state.

Read aloud: a node state keeps its own justified block. -/
theorem justifiedFrom_refl (C : Config) (n : M.N) : JustifiedFrom M C n n :=
  Or.inl rfl

/-- `JustifiedFrom` is transitive.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `n`, `n'`, `n''`: the three node states.

Read aloud: `JustifiedFrom` composes. -/
theorem justifiedFrom_trans (C : Config) {n n' n'' : M.N} (h : JustifiedFrom M C n n')
    (h' : JustifiedFrom M C n' n'') : JustifiedFrom M C n n'' := by
  rcases h' with h' | h'
  · rcases h with h | h
    · exact Or.inl (h'.trans h)
    · obtain ⟨D, hD⟩ := h
      exact Or.inr ⟨D, h'.trans hD⟩
  · exact Or.inr h'

/-- Two node states with the same justified block are related by `JustifiedFrom`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `n`, `n'`: the two node states.

Read aloud: a step that keeps the justified block relates its input to its output. -/
theorem justifiedFrom_of_frame (C : Config) {n n' : M.N} (hJ : n'.justified = n.justified) :
    JustifiedFrom M C n n' :=
  Or.inl hJ

/-- A node state holds its own blocks, votes and stamps.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state.

Read aloud: `TreeGrows` holds from a node state to itself. -/
theorem TreeGrows.refl (n : M.N) : TreeGrows M n n :=
  ⟨Finset.Subset.refl _, ancestorEq_refl _, fun _ => List.prefix_refl _, fun _ _ => rfl,
    fun _ _ _ => rfl⟩

/-- A wake keeps the node's blocks, votes and stamps: `TreeGrows` holds from a node state to its
wake, from the facts of the wake (`F.wk.wake_readers`). The landed counterpart is the equation
`wake_eq` (a wake writes `awakeSince` and the clock only) followed by `TreeGrows.refl`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`: the wake time.

Read aloud: waking forgets no block, vote or stamp. -/
theorem TreeGrows.of_wake (n : M.N) (t : Time) : TreeGrows M n (M.wake n t) := by
  obtain ⟨-, -, hT, hF, -, -, -, hV, hVS, hBS, -⟩ := F.wk.wake_readers n t
  refine ⟨?_, ?_, fun s => ?_, fun B _ => ?_, fun s vote _ => ?_⟩
  · show n.tree ⊆ M.tree (M.wake n t)
    rw [hT]
  · show n.finalized.AncestorEq (M.finalized (M.wake n t))
    rw [hF]
    exact ancestorEq_refl _
  · show n.votesHeld s <+: M.votesHeld (M.wake n t) s
    rw [hV]
  · show M.blockStamp (M.wake n t) B = n.blockStamp B
    rw [hBS]
  · show M.voteStamp (M.wake n t) vote = n.voteStamp vote
    rw [hVS]

/-- A wake keeps the votes filed by slot, from the facts of the wake (`F.wk.wake_readers`).

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`: the wake time; `h`: `n`'s votes are filed by slot.

Read aloud: waking keeps the votes filed by slot. -/
theorem slotKeyed_wake {n : M.N} {t : Time} (h : SlotKeyed M n) : SlotKeyed M (M.wake n t) := by
  intro s vote hv
  have hV := (F.wk.wake_readers n t).2.2.2.2.2.2.2.1
  change vote ∈ M.votesHeld (M.wake n t) s at hv
  rw [hV] at hv
  exact h s vote hv

end

/-- `TreeGrows` is transitive.

The variables:
- `M`: the model (implicit, so that `h.trans h'` reads it off `h`);
- `n`, `n'`, `n''`: the three node states.

Read aloud: `TreeGrows` composes. -/
theorem TreeGrows.trans {M : GoldilocksModel V} {n n' n'' : M.N} (h : TreeGrows M n n')
    (h' : TreeGrows M n' n'') : TreeGrows M n n'' := by
  obtain ⟨hT, hF, hV, hB, hS⟩ := h
  obtain ⟨hT', hF', hV', hB', hS'⟩ := h'
  refine ⟨hT.trans hT', ancestorEq_trans hF hF', fun s => (hV s).trans (hV' s),
    fun B hBT => ?_, fun s vote hv => ?_⟩
  · rw [hB' B (hT hBT), hB B hBT]
  · rw [hS' s vote ((hV s).subset hv), hS s vote hv]

/-! ## At the spec's model -/

/-- At the spec's model, `StampsAt` is the landed definition.

The variables:
- `n`, `n'`: the two node states.

Read aloud: the spec's model has the landed `StampsAt`. -/
@[record_goldilocks]
theorem goldilocks_StampsAt (n n' : NodeState V) :
    GoldilocksCorrectness.Proofs.Routines.StampsAt n n' = StampsAt Model.goldilocks n n' := rfl

/-- At the spec's model, `FinalizedFrom` is the landed definition.

The variables:
- `C`: the parameters; `n`, `n'`: the two node states.

Read aloud: the spec's model has the landed `FinalizedFrom`. -/
@[record_goldilocks]
theorem goldilocks_FinalizedFrom (C : Config) (n n' : NodeState V) :
    GoldilocksCorrectness.Proofs.Routines.FinalizedFrom C n n' =
      FinalizedFrom Model.goldilocks C n n' := rfl

/-- At the spec's model, `JustifiedFrom` is the landed definition.

The variables:
- `C`: the parameters; `n`, `n'`: the two node states.

Read aloud: the spec's model has the landed `JustifiedFrom`. -/
@[record_goldilocks]
theorem goldilocks_JustifiedFrom (C : Config) (n n' : NodeState V) :
    GoldilocksCorrectness.Proofs.Routines.JustifiedFrom C n n' =
      JustifiedFrom Model.goldilocks C n n' := rfl

/-- At the spec's model, `TreeGrows` is the landed definition.

The variables:
- `n`, `n'`: the two node states.

Read aloud: the spec's model has the landed `TreeGrows`. -/
@[record_goldilocks]
theorem goldilocks_TreeGrows (n n' : NodeState V) :
    GoldilocksCorrectness.Proofs.Routines.TreeGrows n n' = TreeGrows Model.goldilocks n n' := rfl

/-- The landed `GoldilocksCorrectness.Proofs.Routines.StampsAt.refl`, recovered from its record
form at the spec's model.

Read aloud: the landed `StampsAt.refl` holds, as the record's theorem at the spec's model. -/
theorem StampsAt.refl_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.StampsAt.refl V) := by
  try simp only [record_goldilocks]
  exact StampsAt.refl (Model.goldilocks (V := V)) goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.StampsAt.congr_left`, recovered from its
record form at the spec's model: two node states with the same FG state and AC state have the same
tree and votes held.

Read aloud: the landed `StampsAt.congr_left` holds, as the record's theorem at the spec's model. -/
theorem StampsAt.congr_left_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.StampsAt.congr_left V) := by
  intro n₀ n n' hS hA h
  rw [goldilocks_StampsAt] at h ⊢
  exact StampsAt.congr_left (Model.goldilocks (V := V)) goldilocksFacts
    (show n₀.S.T = n.S.T by rw [hS]) (show n₀.A.gf_votes = n.A.gf_votes by rw [hA]) h

/-- The landed `GoldilocksCorrectness.Proofs.Routines.finalizedFrom_refl`, recovered from its
record form at the spec's model.

Read aloud: the landed `finalizedFrom_refl` holds, as the record's theorem at the spec's model. -/
theorem finalizedFrom_refl_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.finalizedFrom_refl V _ _) := by
  try simp only [record_goldilocks]
  exact finalizedFrom_refl (Model.goldilocks (V := V)) goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.finalizedFrom_trans`, recovered from its
record form at the spec's model.

Read aloud: the landed `finalizedFrom_trans` holds, as the record's theorem at the spec's model. -/
theorem finalizedFrom_trans_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.finalizedFrom_trans V _ _) := by
  try simp only [record_goldilocks]
  exact finalizedFrom_trans (Model.goldilocks (V := V)) goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.finalizedFrom_of_frame`, recovered from its
record form at the spec's model.

Read aloud: the landed `finalizedFrom_of_frame` holds, as the record's theorem at the spec's
model. -/
theorem finalizedFrom_of_frame_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.finalizedFrom_of_frame V _ _) := by
  try simp only [record_goldilocks]
  exact finalizedFrom_of_frame (Model.goldilocks (V := V)) goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.initial_finalizedFromChain`, recovered from
its record form at the spec's model.

Read aloud: the landed `initial_finalizedFromChain` holds, as the record's theorem at the spec's
model. -/
theorem initial_finalizedFromChain_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.initial_finalizedFromChain V _ _) := by
  try simp only [record_goldilocks]
  exact initial_finalizedFromChain (Model.goldilocks (V := V)) goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.justifiedFrom_refl`, recovered from its
record form at the spec's model.

Read aloud: the landed `justifiedFrom_refl` holds, as the record's theorem at the spec's model. -/
theorem justifiedFrom_refl_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.justifiedFrom_refl V _ _) := by
  try simp only [record_goldilocks]
  exact justifiedFrom_refl (Model.goldilocks (V := V)) goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.justifiedFrom_trans`, recovered from its
record form at the spec's model.

Read aloud: the landed `justifiedFrom_trans` holds, as the record's theorem at the spec's model. -/
theorem justifiedFrom_trans_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.justifiedFrom_trans V _ _) := by
  try simp only [record_goldilocks]
  exact justifiedFrom_trans (Model.goldilocks (V := V)) goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.justifiedFrom_of_frame`, recovered from its
record form at the spec's model.

Read aloud: the landed `justifiedFrom_of_frame` holds, as the record's theorem at the spec's
model. -/
theorem justifiedFrom_of_frame_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.justifiedFrom_of_frame V _ _) := by
  try simp only [record_goldilocks]
  exact justifiedFrom_of_frame (Model.goldilocks (V := V)) goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.TreeGrows.refl`, recovered from its record
form at the spec's model.

Read aloud: the landed `TreeGrows.refl` holds, as the record's theorem at the spec's model. -/
theorem TreeGrows.refl_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.TreeGrows.refl V _) := by
  try simp only [record_goldilocks]
  exact TreeGrows.refl (Model.goldilocks (V := V)) goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.TreeGrows.trans`, recovered from its record
form at the spec's model.

Read aloud: the landed `TreeGrows.trans` holds, as the record's theorem at the spec's model. -/
theorem TreeGrows.trans_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.TreeGrows.trans V _) := by
  try simp only [record_goldilocks]
  exact TreeGrows.trans (M := Model.goldilocks (V := V))

end GoldilocksCorrectness.Record.Proofs.Routines
