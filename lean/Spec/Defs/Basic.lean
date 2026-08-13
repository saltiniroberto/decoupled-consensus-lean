import StsMultisetLog.Spec.Message
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# The vocabulary Figures 1 and 2 need

*Height Filtering and Healing for a Simplex-Style Finality Variant*
(`height_filter_healing.tex`), Sections 2 and 3.

This file is **not** a figure. It carries exactly those numbered definitions that
Figure 1 (`alg:state-replay`) or Figure 2 (`alg:attestation-processing`) reads, and nothing
else. The slashing rules, the durable signing history, state-height, derived certificates
and the store are all stated in the same sections and are all absent, because neither
figure mentions them.

What is here, by the paper's numbering:

* Definition 3 (`def:validator-weights`) — `Electorate`, `w(·)`, `W`, `q`, `m`.
* Definition 4 (`def:height`) — `Params.K`, `Params.Ddebt`.
* Definition 5 (`def:block-chain`) — `Blk`, `ancestors`, `⪯`, `≺`, `∼`.
* Definition 8 (`def:fg-message`) — `Attestation`, `HeightPair`, `FinalityPair`.
* Definition 9 (`def:valid-attestation-inclusion`) — `ValidInclusion`.
* Definition 13 (`def:chain-state`) — `ChainState`, `ChainState.gen`.
* Definition 14 (`def:nonjustifiable`) — `nonjustifiable`.
* Definition 15 (`def:participation-state`) — `ChainState.Qtarget`, `ChainState.Qprog`.
* Definition 24 (`def:total-raw-replay`) — `TransitionResult`, for the `invalid` the two
  figures return.

## A block is its content

Definition 5 (`def:block-chain`) computes a root from a block's canonical encoding and then
says "from then on we identify the block with its root", with the collision resistance of
Assumption 4 (`ass:crypto`) behind it. `Blk` makes that identification structural: it is an
inductive type whose two constructors are the definition's two cases, so two blocks are
equal exactly when their contents are.

What that buys: `ancestors` recurses on a constructor argument, so `⪯` needs neither a
`termination_by` nor a hypothesis that a block's slot exceeds its parent's — and that slot
condition is a check Definition 24 (`def:total-raw-replay`) states, not an invariant of the
datatype. A datatype forbidding it would say that a badly built block cannot be *received*,
which is the opposite of what the paper's store does with one.

What it costs: `deriving DecidableEq` does not reach this family. Measured here, not
inherited — see `CONTEXT.md` for what was tried. So the decision procedure is written out
by hand below, under "Decidable equality, written out". Nothing in this file or in the
figure files is `noncomputable`.

`Blk` and `Attestation` are one `mutual` family because each names the other: a block
carries attestations, and an attestation names blocks in its head and in both of its pairs.

## A signature is its `validator` field

Definition 5 (`def:block-chain`) has a block carry *signed* attestations, and
Definition 9 (`def:valid-attestation-inclusion`) asks that each verify under the named
validator's key. Here an `Attestation` carries the plain `validator` field and no
signature, so a block naming a validator that never signed is representable and
`ValidInclusion` cannot reject it.

That is a hole, and it is deliberate at this stage: what closes it is the execution layer,
where an attestation reaches a block only by having been sent, and the framework's
`Framework.StsMultisetLog.SignedMsg` makes sending under `sender = p` the same thing as
being signed by `p`. Nothing in Figures 1 and 2 depends on which of the two shapes is
chosen, and the choice is recorded in `CONTEXT.md` so that the execution layer settles it
rather than inherits it.

## `⊥`

The paper writes `⊥` for the absent target, the absent height and the absent SG head. That
is `Option.none` here, given the `⊥` spelling by a scoped `Bot` instance, so `σ.T_h ≠ ⊥` is
literal Lean.

The *pairs* are inductive types rather than pairs of `Option`s. Definition 8
(`def:fg-message`) admits `(h, T)`, `(h, ⊥)` and `(⊥, ⊥)` and not `(⊥, T)`, and an
inductive type is how the fourth combination is made unrepresentable. The definition's four
field names are recovered as accessors below.
-/

set_option autoImplicit false

namespace Decoupled

open Framework.StsMultisetLog

/-- `⊥` for an absent block, height or head, as the paper writes it. Scoped, so it cannot
    leak into a file that means something else by `⊥`. -/
scoped instance {α : Type} : Bot (Option α) := ⟨none⟩

/-! ## Definition 3 (`def:validator-weights`) — fixed validator weights -/

/-- Definition 3 (`def:validator-weights`): a fixed validator set `V` and a fixed positive
    integer weight `w(i)` for each of its members.

    A class, so that `w(·)`, `W`, `q` and `m` read as the paper writes them with no
    parameter threaded through every signature. Assumption 1 (`ass:fixed-electorate`) is
    what licenses that: "every chain and round uses the fixed identities and weights". -/
class Electorate (Node : Type) where
  /-- The validator set `V`. -/
  V : Finset Node
  /-- Validator `i`'s fixed weight `w(i)`. -/
  w : Node → Nat
  /-- Weights are positive. -/
  w_pos : ∀ i ∈ V, 0 < w i

variable {Node Root : Type}

section Weights
variable [Electorate Node]

/-- `w(S) = ∑_{i ∈ S} w(i)` (Definition 3, `def:validator-weights`). -/
def weight (S : Finset Node) : Nat := ∑ i ∈ S, Electorate.w i

@[inherit_doc] scoped notation:max "w(" S ")" => weight S

end Weights

/-- `W = ∑_{i ∈ V} w(i)`, the total weight (Definition 3, `def:validator-weights`). -/
def W (Node : Type) [Electorate Node] : Nat := w(Electorate.V (Node := Node))

/-- `q = ⌈2W/3⌉`, the finality quorum threshold (Definition 3, `def:validator-weights`).
    Written in `Nat` arithmetic; that definition notes a check against it may equivalently
    be written `3w(Q) ≥ 2W`. -/
def q (Node : Type) [Electorate Node] : Nat := (2 * W Node + 2) / 3

/-- `m = ⌊W/2⌋ + 1`, the strict-majority threshold (Definition 3, `def:validator-weights`).
    No routine in Figures 1 (`alg:state-replay`) or 2 (`alg:attestation-processing`) uses
    it; it is here because it is part of the same definition. -/
def m (Node : Type) [Electorate Node] : Nat := W Node / 2 + 1

section Thresholds
variable [Electorate Node]

/-- Definition 3 (`def:validator-weights`): `S` is a *quorum*, `w(S) ≥ q`.

    A predicate taking the set, rather than a bare `q`: `W`, `q` and `m` are constants of
    the electorate and nothing in their types mentions `Node`, so written bare they leave
    the electorate undetermined. The notation below restores the paper's spelling at the
    use site. -/
def Quorum (S : Finset Node) : Prop := w(S) ≥ q Node

@[inherit_doc] scoped notation:50 "w(" S ")≥q" => Quorum S

/-- Definition 3 (`def:validator-weights`): `S` is a *strict majority*, `w(S) ≥ m`,
    equivalently `2w(S) > W`. -/
def StrictMajority (S : Finset Node) : Prop := w(S) ≥ m Node

@[inherit_doc] scoped notation:50 "w(" S ")≥m" => StrictMajority S

instance (S : Finset Node) : Decidable (Quorum S) := inferInstanceAs (Decidable (_ ≥ _))

instance (S : Finset Node) : Decidable (StrictMajority S) :=
  inferInstanceAs (Decidable (_ ≥ _))

end Thresholds

/-! ## Definition 4 (`def:height`) — height -/

/-- The two protocol constants Definition 4 (`def:height`) fixes: `K`, the period at which a
    height is *eligible* to be nonjustifiable, and `D_debt`, the finality debt that has to
    have accumulated before that eligibility bites. -/
class Params where
  /-- Every `K`-th height is eligible to be nonjustifiable. -/
  K : Nat
  /-- Justification is disabled at such a height only once the debt exceeds this. -/
  Ddebt : Nat
  /-- `K ≥ 2`. -/
  K_ge : 2 ≤ K
  /-- `D_debt ≥ 1`. -/
  Ddebt_ge : 1 ≤ Ddebt

/-! ## Definitions 5 and 8 — blocks and attestations, as one mutual family -/

mutual

/-- Definition 5 (`def:block-chain`). "Genesis has no parent. Every other block has one
    parent, a slot greater than its parent's slot, a signature by the proposer assigned to
    that slot, a finite canonically ordered set of signed attestations, and a claimed
    post-state root."

    The two constructors are those two cases. The slot condition is **not** enforced here:
    it is one of the checks Definition 24 (`def:total-raw-replay`) states, and a block
    failing it has to be representable, because the store receives one. -/
inductive Blk (Node Root : Type) where
  /-- `B_genesis`. -/
  | genesis
  /-- Every other block. -/
  | mk (parent : Blk Node Root) (slot : Time) (proposer : Node)
      (attestations : List (Attestation Node Root)) (claimedRoot : Root)

/-- Definition 8 (`def:fg-message`). One signed object carrying the stabilization head, the
    current-height choice and an independent finality commitment. -/
structure Attestation (Node Root : Type) where
  /-- `v.validator`. See the module header on what this stands in for. -/
  validator : Node
  /-- `v.round`, the globally unique round the attestation is cast in. -/
  round : Nat
  /-- `v.head`, the stabilization head: a block or `⊥`. Raw SG evidence, which
      Definition 9 (`def:valid-attestation-inclusion`) keeps out of block validity. -/
  head : Option (Blk Node Root)
  /-- `(v.height, v.target)`. -/
  heightPair : HeightPair Node Root
  /-- `(v.finalize_height, v.finalize_target)`. -/
  finalityPair : FinalityPair Node Root

/-- Definition 8 (`def:fg-message`)'s height pair: a target vote `(h, T)` with `T ≠ ⊥`, a
    timeout vote `(h, ⊥)`, or the empty pair `(⊥, ⊥)`. `(⊥, T)` is not a case, which is the
    reason this is an inductive type rather than two `Option` fields. -/
inductive HeightPair (Node Root : Type) where
  /-- `(h, T)` with `T ≠ ⊥`. -/
  | target (h : Nat) (T : Blk Node Root)
  /-- `(h, ⊥)`. -/
  | timeout (h : Nat)
  /-- `(⊥, ⊥)`. Definition 11 (`def:slashing`) needs this to have height `⊥`, so that it
      conflicts with neither pair. -/
  | empty

/-- Definition 8 (`def:fg-message`)'s finality pair: `(h_f, T_f)` with `T_f ≠ ⊥`, or the
    empty pair. -/
inductive FinalityPair (Node Root : Type) where
  /-- `(h_f, T_f)` with `T_f ≠ ⊥`. -/
  | commit (h : Nat) (T : Blk Node Root)
  /-- The empty pair. -/
  | empty

end

/-! ### Decidable equality, written out

`deriving DecidableEq` does not reach this family. The error names every type in it:

    None of the deriving handlers for class `DecidableEq` applied to
    `Blk`, `Attestation`, and `HeightPair`

and it is the nesting through `List` and `Option` that stops it, not the `mutual` — measured
by de-nesting, which makes the same `deriving` line succeed. See `CONTEXT.md`.

Equality here is decidable all the same: a block is a finite tree and comparing two of them
is a structural recursion. So the procedure is written out rather than assumed. The
alternative, `Classical.propDecidable`, has type `(a : Prop) → Decidable a` and is built from
`Classical.choice`: it produces a `Decidable` value carrying no algorithm, which is what used
to make `⪯` and all seven routines of Figures 1 and 2 `noncomputable`.

**Six functions, not four.** `attListBeq` and `optBlkBeq` carry the nesting, and they are
precisely what the deriving handler will not generate. Termination is inferred; no
`termination_by` is needed.

**What this costs: `[DecidableEq Root]`.** A block carries a `claimedRoot`, so deciding block
equality means deciding root equality. Every section that compares two blocks now assumes it,
including the figure files.

**`by decide` still does not work on these.** The mutual block compiles through
`blkBeq._mutual` over a `PSum`, which is well-founded rather than structural recursion, so
`blkBeq .genesis .genesis` is not definitionally `true`. Proofs go through the equation
lemmas — `simp [blkBeq]` — as the soundness theorems below do. Reduction was not available
under the classical instance either, so nothing was lost.
-/

section DecEq
variable [DecidableEq Node] [DecidableEq Root]

mutual

/-- Structural equality of blocks (Definition 5, `def:block-chain`). -/
def blkBeq : Blk Node Root → Blk Node Root → Bool
  | .genesis, .genesis => true
  | .mk p s n as r, .mk p' s' n' as' r' =>
      blkBeq p p' && s == s' && decide (n = n') && attListBeq as as' && decide (r = r')
  | _, _ => false

/-- Structural equality of attestations (Definition 8, `def:fg-message`). -/
def attBeq : Attestation Node Root → Attestation Node Root → Bool
  | ⟨v, rd, hd, hp, fp⟩, ⟨v', rd', hd', hp', fp'⟩ =>
      decide (v = v') && rd == rd' && optBlkBeq hd hd' && heightPairBeq hp hp' &&
        finalityPairBeq fp fp'

/-- The `List` half of the nesting: a block's attestations, compared pairwise. -/
def attListBeq : List (Attestation Node Root) → List (Attestation Node Root) → Bool
  | [], [] => true
  | a :: as, b :: bs => attBeq a b && attListBeq as bs
  | _, _ => false

/-- The `Option` half of the nesting: an attestation's stabilization head. -/
def optBlkBeq : Option (Blk Node Root) → Option (Blk Node Root) → Bool
  | none, none => true
  | some a, some b => blkBeq a b
  | _, _ => false

/-- Structural equality of height pairs (Definition 8, `def:fg-message`). -/
def heightPairBeq : HeightPair Node Root → HeightPair Node Root → Bool
  | .target h T, .target h' T' => h == h' && blkBeq T T'
  | .timeout h, .timeout h' => h == h'
  | .empty, .empty => true
  | _, _ => false

/-- Structural equality of finality pairs (Definition 8, `def:fg-message`). -/
def finalityPairBeq : FinalityPair Node Root → FinalityPair Node Root → Bool
  | .commit h T, .commit h' T' => h == h' && blkBeq T T'
  | .empty, .empty => true
  | _, _ => false

end

mutual

/-- `blkBeq` decides equality of blocks. -/
theorem blkBeq_iff : ∀ (a b : Blk Node Root), blkBeq a b = true ↔ a = b
  | .genesis, .genesis => by simp [blkBeq]
  | .genesis, .mk .. => by simp [blkBeq]
  | .mk .., .genesis => by simp [blkBeq]
  | .mk p s n as r, .mk p' s' n' as' r' => by
      rw [blkBeq, Blk.mk.injEq]
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
      rw [blkBeq_iff p p', attListBeq_iff as as']
      simp only [beq_iff_eq, decide_eq_true_eq]
      simp only [and_assoc]

/-- `attBeq` decides equality of attestations. -/
theorem attBeq_iff : ∀ (a b : Attestation Node Root), attBeq a b = true ↔ a = b
  | ⟨v, rd, hd, hp, fp⟩, ⟨v', rd', hd', hp', fp'⟩ => by
      rw [attBeq, Attestation.mk.injEq]
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
      rw [optBlkBeq_iff hd hd', heightPairBeq_iff hp hp', finalityPairBeq_iff fp fp']
      simp only [beq_iff_eq, decide_eq_true_eq]
      simp only [and_assoc]

/-- `attListBeq` decides equality of attestation lists. -/
theorem attListBeq_iff :
    ∀ (a b : List (Attestation Node Root)), attListBeq a b = true ↔ a = b
  | [], [] => by simp [attListBeq]
  | [], _ :: _ => by simp [attListBeq]
  | _ :: _, [] => by simp [attListBeq]
  | a :: as, b :: bs => by
      rw [attListBeq, Bool.and_eq_true, attBeq_iff a b, attListBeq_iff as bs]
      simp

/-- `optBlkBeq` decides equality of optional blocks. -/
theorem optBlkBeq_iff : ∀ (a b : Option (Blk Node Root)), optBlkBeq a b = true ↔ a = b
  | none, none => by simp [optBlkBeq]
  | none, some _ => by simp [optBlkBeq]
  | some _, none => by simp [optBlkBeq]
  | some a, some b => by rw [optBlkBeq, blkBeq_iff a b]; simp

/-- `heightPairBeq` decides equality of height pairs. -/
theorem heightPairBeq_iff : ∀ (a b : HeightPair Node Root), heightPairBeq a b = true ↔ a = b
  | .target h T, .target h' T' => by
      rw [heightPairBeq, Bool.and_eq_true, blkBeq_iff T T']
      simp only [beq_iff_eq, HeightPair.target.injEq]
  | .timeout _, .timeout _ => by simp [heightPairBeq]
  | .empty, .empty => by simp [heightPairBeq]
  | .target .., .timeout _ => by simp [heightPairBeq]
  | .target .., .empty => by simp [heightPairBeq]
  | .timeout _, .target .. => by simp [heightPairBeq]
  | .timeout _, .empty => by simp [heightPairBeq]
  | .empty, .target .. => by simp [heightPairBeq]
  | .empty, .timeout _ => by simp [heightPairBeq]

/-- `finalityPairBeq` decides equality of finality pairs. -/
theorem finalityPairBeq_iff :
    ∀ (a b : FinalityPair Node Root), finalityPairBeq a b = true ↔ a = b
  | .commit h T, .commit h' T' => by
      rw [finalityPairBeq, Bool.and_eq_true, blkBeq_iff T T']
      simp only [beq_iff_eq, FinalityPair.commit.injEq]
  | .empty, .empty => by simp [finalityPairBeq]
  | .commit .., .empty => by simp [finalityPairBeq]
  | .empty, .commit .. => by simp [finalityPairBeq]

end

instance : DecidableEq (Blk Node Root) := fun a b => decidable_of_iff _ (blkBeq_iff a b)

instance : DecidableEq (Attestation Node Root) :=
  fun a b => decidable_of_iff _ (attBeq_iff a b)

instance : DecidableEq (HeightPair Node Root) :=
  fun a b => decidable_of_iff _ (heightPairBeq_iff a b)

instance : DecidableEq (FinalityPair Node Root) :=
  fun a b => decidable_of_iff _ (finalityPairBeq_iff a b)

end DecEq

namespace Blk

/-- `B.parent`, `⊥` at genesis. -/
def parent : Blk Node Root → Option (Blk Node Root)
  | .genesis => ⊥
  | .mk p _ _ _ _ => some p

/-- `B.slot`. Genesis is at slot 0, which is what Definition 7
    (`def:current-height-target`) states as `(s_1, T_1) = (0, B_genesis)`. -/
def slot : Blk Node Root → Time
  | .genesis => 0
  | .mk _ s _ _ _ => s

/-- The validator whose signature the block carries. `⊥` at genesis, which has none. -/
def proposer : Blk Node Root → Option Node
  | .genesis => ⊥
  | .mk _ _ p _ _ => some p

/-- `B.attestations`, the finite canonically ordered list. Empty at genesis. -/
def attestations : Blk Node Root → List (Attestation Node Root)
  | .genesis => []
  | .mk _ _ _ a _ => a

/-- The post-state root the block claims. `⊥` at genesis, whose state is stipulated rather
    than claimed. -/
def claimedRoot : Blk Node Root → Option Root
  | .genesis => ⊥
  | .mk _ _ _ _ r => some r

end Blk

namespace Attestation

/-- `v.height`. -/
def height (a : Attestation Node Root) : Option Nat :=
  match a.heightPair with
  | .target h _ => some h
  | .timeout h => some h
  | .empty => ⊥

/-- `v.target`. -/
def target (a : Attestation Node Root) : Option (Blk Node Root) :=
  match a.heightPair with
  | .target _ T => some T
  | .timeout _ => ⊥
  | .empty => ⊥

/-- `v.finalize_height`. -/
def finalizeHeight (a : Attestation Node Root) : Option Nat :=
  match a.finalityPair with
  | .commit h _ => some h
  | .empty => ⊥

/-- `v.finalize_target`. -/
def finalizeTarget (a : Attestation Node Root) : Option (Blk Node Root) :=
  match a.finalityPair with
  | .commit _ T => some T
  | .empty => ⊥

end Attestation

/-! ## Definition 5 (`def:block-chain`) — ancestry -/

section Tree

/-- The block and all of its ancestors, nearest first. Structural recursion: the recursive
    call is on a constructor argument. Takes no `DecidableEq`: walking the chain does not
    compare blocks, only deciding membership in the result does. -/
def ancestors : Blk Node Root → List (Blk Node Root)
  | .genesis => [.genesis]
  | .mk p s n a r => .mk p s n a r :: ancestors p

/-- `B ⪯ C`: `B = C`, or `B` is an ancestor of `C`. Definition 5 (`def:block-chain`) makes
    "descendant" reflexive, and this is that relation. -/
def Preceq (a b : Blk Node Root) : Prop := a ∈ ancestors b

@[inherit_doc] scoped infix:50 " ⪯ " => Preceq

section Decide
variable [DecidableEq Node] [DecidableEq Root]

instance : DecidableRel (Preceq (Node := Node) (Root := Root)) :=
  fun a b => inferInstanceAs (Decidable (a ∈ ancestors b))

/-- `B ≺ C`: strict ancestry (Definition 5, `def:block-chain`). -/
def Prec (a b : Blk Node Root) : Prop := a ⪯ b ∧ a ≠ b

@[inherit_doc] scoped infix:50 " ≺ " => Prec

instance : DecidableRel (Prec (Node := Node) (Root := Root)) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- `B ∼ C`: compatible, one precedes the other (Definition 5, `def:block-chain`).
    Unused by Figures 1 (`alg:state-replay`) and 2 (`alg:attestation-processing`); part of
    the same definition. -/
def Compatible (a b : Blk Node Root) : Prop := a ⪯ b ∨ b ⪯ a

@[inherit_doc] scoped infix:50 " ∼ " => Compatible

instance : DecidableRel (Compatible (Node := Node) (Root := Root)) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- `B` and `C` conflict: Definition 5 (`def:block-chain`)'s "otherwise they conflict",
    which is the negation of `∼`. Two blocks conflict exactly when they lie on different
    branches. Read by no figure, and named because the paper's results are stated over it. -/
def Conflicts (a b : Blk Node Root) : Prop := ¬ (a ∼ b)

instance : DecidableRel (Conflicts (Node := Node) (Root := Root)) :=
  fun _ _ => inferInstanceAs (Decidable (¬ _))

end Decide

end Tree

/-! ## Definition 9 (`def:valid-attestation-inclusion`) — valid attestation inclusion -/

section Inclusion
variable [DecidableEq Node] [Electorate Node]

/-- Definition 9 (`def:valid-attestation-inclusion`), minus what this file's idealization
    of signing discharges. The definition asks for a valid signature, well-formedness under
    the canonical encoding, membership of the named validator in `V`, and verification
    under that validator's key. Encodings are not modelled and signatures are the
    `validator` field, so the one condition left to check is membership in `V`.

    Note what the definition explicitly does *not* ask: a root named by an attestation is
    not a block-validity condition, and an unknown stabilization head cannot invalidate a
    block. -/
def ValidInclusion (a : Attestation Node Root) : Bool := decide (a.validator ∈ Electorate.V)

end Inclusion

/-! ## Definition 13 (`def:chain-state`) — the chain state -/

/-- Definition 13 (`def:chain-state`).
    `σ = (L, s, h, s_h, T_h, nj, target_participation, progress, J, h_j, F, h_F, P)`, in
    the paper's order. -/
structure ChainState (Node Root : Type) where
  /-- `L`, the latest block. -/
  L : Blk Node Root
  /-- `s`, the slot the chain has closed up to. A block post-state leaves `s = L.slot`; each
      `process_slot` closes the slot at `s` and then increments it. -/
  s : Time
  /-- `h`, the current height. -/
  h : Nat
  /-- `s_h`, the current height's start slot. -/
  s_h : Time
  /-- `T_h`, the current height's target, `⊥` until its root can be named. -/
  T_h : Option (Blk Node Root)
  /-- `nj`, whether justification is disabled at `h`. Set when the chain enters `h` and
      unchanged until the next height transition. -/
  nj : Bool
  /-- `target_participation[i]`: `i` voted for the exact stored target. -/
  targetParticipation : Node → Bool
  /-- `progress[i]`: `i` made a current-height message that proves progress. -/
  progress : Node → Bool
  /-- `J`, the latest justified block. -/
  J : Blk Node Root
  /-- `h_j`, its height. -/
  h_j : Nat
  /-- `F`, the greatest finalized block. -/
  F : Blk Node Root
  /-- `h_F`, its height. -/
  h_F : Nat
  /-- `P`, the validators whose finalize pairs were accepted while `(J, h_j)` was the
      latest unfinalized justification. -/
  P : Finset Node

section State
variable [DecidableEq Node] [Electorate Node]

/-- `σ_gen`: the initial values Definition 13 (`def:chain-state`) lists, and the **Genesis**
    block of Figure 1 (`alg:state-replay`), which states the same ones. Height 1, genesis
    justified and finalized at height 0, genesis already the height-1 target, both
    participation arrays empty. -/
def ChainState.gen : ChainState Node Root where
  L := .genesis
  s := 0
  h := 1
  s_h := 0
  T_h := some .genesis
  nj := false
  targetParticipation _ := false
  progress _ := false
  J := .genesis
  h_j := 0
  F := .genesis
  h_F := 0
  P := ∅

/-- Definition 15 (`def:participation-state`):
    `Q_target(σ) = {i : target_participation[i] = true}`, intersected with the electorate,
    since only `V`'s weights are ever summed. -/
def ChainState.Qtarget (σ : ChainState Node Root) : Finset Node :=
  Electorate.V.filter fun i => σ.targetParticipation i

/-- Definition 15 (`def:participation-state`): `Q_prog(σ) = {i : progress[i] = true}`,
    likewise. -/
def ChainState.Qprog (σ : ChainState Node Root) : Finset Node :=
  Electorate.V.filter fun i => σ.progress i

end State

/-! ## Definition 14 (`def:nonjustifiable`) — the flag -/

section Nonjustifiable
variable [Params]

/-- Definition 14 (`def:nonjustifiable`): the flag a chain sets when it enters height `h`
    from a post-finality state with finalized height `h_F`,
    `nj = (K ∣ h) ∧ (h - h_F > D_debt)`.

    Written with the paper's truncated difference, `Nat` subtraction being exactly that. -/
def nonjustifiable (h hF : Nat) : Bool :=
  decide (Params.K ∣ h ∧ h - hF > Params.Ddebt)

end Nonjustifiable

/-! ## Definition 24 (`def:total-raw-replay`) — what the transition returns -/

/-- Definition 24 (`def:total-raw-replay`): the transition "is evaluated as a total
    operation returning either a state or `invalid`; a failed precondition or transition
    check returns `invalid` to the caller".

    One constructor per symbol the paper writes, rather than `Option (ChainState …)`.
    `Option.none` is already spoken for: `⊥` renders the absent target, height and head of
    Definitions 8 (`def:fg-message`) and 13 (`def:chain-state`), and `invalid` is a
    different symbol. The `Coe` below is what lets a routine of this return type end with
    the paper's bare `return σ`.

    Only `process_block` and `state_transition` return this. Every other routine of
    Figures 1 (`alg:state-replay`) and 2 (`alg:attestation-processing`) is a total
    `σ → σ`, which is the shape those figures show. -/
inductive TransitionResult (Node Root : Type) where
  /-- The transition produced a state. -/
  | state (σ : ChainState Node Root)
  /-- A failed precondition or transition check. -/
  | invalid

@[inherit_doc] scoped notation "invalid" => TransitionResult.invalid

/-- So that a routine returning a `TransitionResult` can end with the paper's bare
    `return σ`. -/
instance : Coe (ChainState Node Root) (TransitionResult Node Root) := ⟨.state⟩

end Decoupled
