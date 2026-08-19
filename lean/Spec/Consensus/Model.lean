import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# The draft's model, as far as the rendered figures consume it

This is the rendering of `consensus.pdf`, the human-controlled draft committed at the
repository root. The file holds the model vocabulary the figure files read, and nothing
else: a definition lands here at the moment a figure first consumes it, so everything below
has a consumer under `Spec/Consensus/`.

**Nothing is shared with the old rendering** under `Spec/Defs/` (namespace `Decoupled`).
The draft changed the base types themselves — a block now carries a proposal root — and the
old apparatus is frozen as the record, so this subtree defines its own types in its own
namespace and duplicates the notation layer (`Spec/Consensus/Notation.lean`). Decided
2026-08-19.

**`consensus.pdf` has no stable labels or line numbers and is under revision**, so nothing
here cites it in the checked sense. A docstring saying "Definition 6 of the draft" names the
draft's numbering as of 2026-08-19, and the docstring's own text is what the Lean is read
against.

What Figure 1 (State transition) consumes, and this file therefore holds:

* the validator set and weights — `Electorate`, `w(·)`, `W`, `q`, `m`, `Quorum`, `Majority`;
* the protocol constants `K` and `D` of the height events — `Params`;
* blocks and ancestry — `Block`, `ancestors`, `⪯`;
* attestations and their two pairs — `Attestation`, `HeightPair`, `FinalityPair`.

Absent, because no rendered figure reads them yet: strict ancestry, compatibility and
conflict; rounds, opening slots and the constant `R`; Goldfish votes and committees; the
slashing conditions. Each arrives with its first consumer.

## Block equality is decided by hand

`deriving DecidableEq` does not reach a mutual family nested through `List` and `Option`;
that was measured on the old rendering's identical shape (`Spec/Defs/Basic.lean`, and
`CONTEXT.md` for what was tried). So the decision procedure is written out below, under
"Decidable equality, written out", with the soundness theorems the instances need — the one
kind of proof a `Spec/` file is allowed to hold. Nothing in this subtree is `noncomputable`.

## `⊥`

The draft writes `⊥` for an absent block: the empty target, the empty head, a missing
proposal root. That is `Option.none` here, given the `⊥` spelling by a scoped `Bot`
instance.
-/

set_option autoImplicit false

namespace Consensus

/-- `⊥` for an absent block, height or head, as the draft writes it. Scoped, so it cannot
    leak into a file that means something else by `⊥`. -/
scoped instance {α : Type} : Bot (Option α) := ⟨none⟩

/-! ## Validators and weights -/

/-- The draft's model of validators: a fixed set `V`, and a fixed positive integer weight
    `w(i)` for each member.

    A class, so that `w(·)`, `W`, `q` and `m` read as the draft writes them with no
    parameter threaded through every signature. -/
class Electorate (Validator : Type) where
  /-- The validator set `V`. -/
  V : Finset Validator
  /-- Validator `i`'s fixed weight `w(i)`. -/
  w : Validator → Nat
  /-- Weights are positive. -/
  w_pos : ∀ i ∈ V, 0 < w i

variable {Validator : Type}

section Weights
variable [Electorate Validator]

/-- `w(S) = ∑_{i ∈ S} w(i)`. -/
def weight (S : Finset Validator) : Nat := ∑ i ∈ S, Electorate.w i

@[inherit_doc] scoped notation:max "w(" S ")" => weight S

end Weights

/-- `W = w(V)`, the total weight. -/
def W (Validator : Type) [Electorate Validator] : Nat :=
  w(Electorate.V (Validator := Validator))

/-- `q = ⌈2W/3⌉`, the quorum threshold — the first of the draft's two thresholds used
    throughout. Written in `Nat` arithmetic. -/
def q (Validator : Type) [Electorate Validator] : Nat := (2 * W Validator + 2) / 3

/-- `m = ⌊W/2⌋ + 1`, the majority threshold — the second of the draft's two thresholds.
    No routine of Figure 1 uses it; it is here because the draft defines the two together. -/
def m (Validator : Type) [Electorate Validator] : Nat := W Validator / 2 + 1

section Thresholds
variable [Electorate Validator]

/-- `S` is a *quorum*: `w(S) ≥ q`.

    A predicate taking the set, rather than a bare `q`: `W`, `q` and `m` are constants of
    the electorate and nothing in their types mentions `Validator`, so written bare they
    leave the electorate undetermined. The notation below restores the draft's spelling at
    the use site. -/
def Quorum (S : Finset Validator) : Prop := w(S) ≥ q Validator

@[inherit_doc] scoped notation:50 "w(" S ")≥q" => Quorum S

/-- `S` is a *majority*: `w(S) ≥ m`. -/
def Majority (S : Finset Validator) : Prop := w(S) ≥ m Validator

@[inherit_doc] scoped notation:50 "w(" S ")≥m" => Majority S

instance (S : Finset Validator) : Decidable (Quorum S) := inferInstanceAs (Decidable (_ ≥ _))

instance (S : Finset Validator) : Decidable (Majority S) :=
  inferInstanceAs (Decidable (_ ≥ _))

end Thresholds

/-! ## The height-event constants -/

/-- The two protocol constants of the draft's height events: during prolonged nonfinality
    every `K`-th height becomes nonjustifiable, once finality lags more than `D` heights
    behind. The justify event tests `¬((K ∣ h) ∧ (h − h_F > D))` inline; there is no stored
    flag. -/
class Params where
  /-- Every `K`-th height is eligible to be nonjustifiable. -/
  K : Nat
  /-- Justification is disabled at such a height only once `h − h_F` exceeds this. -/
  D : Nat
  /-- `K ≥ 2`. -/
  K_ge : 2 ≤ K
  /-- `D ≥ 1`. -/
  D_ge : 1 ≤ D

/-! ## Blocks and attestations, as one mutual family

Each names the other: a block carries attestations, and an attestation names blocks in its
head and in both of its pairs. -/

mutual

/-- A block (Definition 1 of the draft). Genesis has no parent and slot 0; every other
    block has a parent, a slot, a list of attestations, and a proposal root — a block or
    `⊥` — which is read only in a round's opening blocks. Chains are in bijection with
    their tips and the draft identifies the two, so this type is both.

    Two deliberate gaps against the draft's sentence:

    * the slot condition — a block's slot exceeds its parent's — is not enforced by the
      datatype, so a badly built block is representable and a store can receive one;
    * the proposer's signature is not modelled here. Proposer assignment is outside the
      draft's scope, and whether a block was signed by its slot's proposer is a fact for
      the execution layer, when one exists. -/
inductive Block (Validator : Type) where
  /-- `B_gen`. -/
  | genesis
  /-- Every other block. -/
  | mk (parent : Block Validator) (slot : Nat)
      (attestations : List (Attestation Validator))
      (proposalRoot : Option (Block Validator))

/-- An attestation (Definition 3 of the draft): the tuple
    `(validator, round, head, height, target, finalize_height, finalize_target)`, signed by
    `validator`. The four height and finality components are carried as the draft's two
    pairs, which is what makes the unwritable combination — a height `⊥` under a named
    target — unrepresentable. The signature itself is not modelled; the `validator` field
    stands in for it, as in `Block`. -/
structure Attestation (Validator : Type) where
  /-- The signing validator. -/
  validator : Validator
  /-- The round the attestation belongs to. -/
  round : Nat
  /-- The head: a block or `⊥`. Read by no rendered figure yet; the draft's Section 4
      gives it meaning. -/
  head : Option (Block Validator)
  /-- The height pair `(height, target)`. -/
  heightPair : HeightPair Validator
  /-- The finality pair `(finalize_height, finalize_target)`. -/
  finalityPair : FinalityPair Validator

/-- An attestation's height pair `(height, target)`: a *target vote* `(h, T)` with
    `T ≠ ⊥`, an *empty-target vote* `(h, ⊥)`, or the empty pair `(⊥, ⊥)`. `(⊥, T)` is not a
    case, which is why this is an inductive type rather than two `Option` fields. -/
inductive HeightPair (Validator : Type) where
  /-- A target vote `(h, T)`. -/
  | target (h : Nat) (T : Block Validator)
  /-- An empty-target vote `(h, ⊥)`. -/
  | emptyTarget (h : Nat)
  /-- The empty pair `(⊥, ⊥)`. -/
  | empty

/-- An attestation's finality pair: `(h_f, T_f)` with `T_f ≠ ⊥`, or the empty pair. -/
inductive FinalityPair (Validator : Type) where
  /-- `(h_f, T_f)` with `T_f ≠ ⊥`. -/
  | pair (h : Nat) (T : Block Validator)
  /-- The empty pair. -/
  | empty

end

/-! ### Decidable equality, written out

Six functions: `attListBeq` and `optBlockBeq` carry the `List` and `Option` nesting, which
is precisely what the deriving handler will not generate. Termination is inferred. The
`…Beq_iff` soundness theorems below are what the `DecidableEq` instances are built from.

`optBlockBeq` serves twice: a block's proposal root and an attestation's head are both
`Option (Block …)`. -/

section DecEq
variable [DecidableEq Validator]

mutual

/-- Structural equality of blocks. -/
def blockBeq : Block Validator → Block Validator → Bool
  | .genesis, .genesis => true
  | .mk p s as pr, .mk p' s' as' pr' =>
      blockBeq p p' && s == s' && attListBeq as as' && optBlockBeq pr pr'
  | _, _ => false

/-- Structural equality of attestations. -/
def attBeq : Attestation Validator → Attestation Validator → Bool
  | ⟨v, rd, hd, hp, fp⟩, ⟨v', rd', hd', hp', fp'⟩ =>
      decide (v = v') && rd == rd' && optBlockBeq hd hd' && heightPairBeq hp hp' &&
        finalityPairBeq fp fp'

/-- The `List` half of the nesting: a block's attestations, compared pairwise. -/
def attListBeq : List (Attestation Validator) → List (Attestation Validator) → Bool
  | [], [] => true
  | a :: as, b :: bs => attBeq a b && attListBeq as bs
  | _, _ => false

/-- The `Option` half of the nesting: a proposal root or a head. -/
def optBlockBeq : Option (Block Validator) → Option (Block Validator) → Bool
  | none, none => true
  | some a, some b => blockBeq a b
  | _, _ => false

/-- Structural equality of height pairs. -/
def heightPairBeq : HeightPair Validator → HeightPair Validator → Bool
  | .target h T, .target h' T' => h == h' && blockBeq T T'
  | .emptyTarget h, .emptyTarget h' => h == h'
  | .empty, .empty => true
  | _, _ => false

/-- Structural equality of finality pairs. -/
def finalityPairBeq : FinalityPair Validator → FinalityPair Validator → Bool
  | .pair h T, .pair h' T' => h == h' && blockBeq T T'
  | .empty, .empty => true
  | _, _ => false

end

mutual

/-- `blockBeq` decides equality of blocks. -/
theorem blockBeq_iff : ∀ (a b : Block Validator), blockBeq a b = true ↔ a = b
  | .genesis, .genesis => by simp [blockBeq]
  | .genesis, .mk .. => by simp [blockBeq]
  | .mk .., .genesis => by simp [blockBeq]
  | .mk p s as pr, .mk p' s' as' pr' => by
      rw [blockBeq, Block.mk.injEq]
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
      rw [blockBeq_iff p p', attListBeq_iff as as', optBlockBeq_iff pr pr']
      simp only [beq_iff_eq]
      simp only [and_assoc]

/-- `attBeq` decides equality of attestations. -/
theorem attBeq_iff : ∀ (a b : Attestation Validator), attBeq a b = true ↔ a = b
  | ⟨v, rd, hd, hp, fp⟩, ⟨v', rd', hd', hp', fp'⟩ => by
      rw [attBeq, Attestation.mk.injEq]
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
      rw [optBlockBeq_iff hd hd', heightPairBeq_iff hp hp', finalityPairBeq_iff fp fp']
      simp only [beq_iff_eq, decide_eq_true_eq]
      simp only [and_assoc]

/-- `attListBeq` decides equality of attestation lists. -/
theorem attListBeq_iff :
    ∀ (a b : List (Attestation Validator)), attListBeq a b = true ↔ a = b
  | [], [] => by simp [attListBeq]
  | [], _ :: _ => by simp [attListBeq]
  | _ :: _, [] => by simp [attListBeq]
  | a :: as, b :: bs => by
      rw [attListBeq, Bool.and_eq_true, attBeq_iff a b, attListBeq_iff as bs]
      simp

/-- `optBlockBeq` decides equality of optional blocks. -/
theorem optBlockBeq_iff : ∀ (a b : Option (Block Validator)), optBlockBeq a b = true ↔ a = b
  | none, none => by simp [optBlockBeq]
  | none, some _ => by simp [optBlockBeq]
  | some _, none => by simp [optBlockBeq]
  | some a, some b => by rw [optBlockBeq, blockBeq_iff a b]; simp

/-- `heightPairBeq` decides equality of height pairs. -/
theorem heightPairBeq_iff : ∀ (a b : HeightPair Validator), heightPairBeq a b = true ↔ a = b
  | .target h T, .target h' T' => by
      rw [heightPairBeq, Bool.and_eq_true, blockBeq_iff T T']
      simp only [beq_iff_eq, HeightPair.target.injEq]
  | .emptyTarget _, .emptyTarget _ => by simp [heightPairBeq]
  | .empty, .empty => by simp [heightPairBeq]
  | .target .., .emptyTarget _ => by simp [heightPairBeq]
  | .target .., .empty => by simp [heightPairBeq]
  | .emptyTarget _, .target .. => by simp [heightPairBeq]
  | .emptyTarget _, .empty => by simp [heightPairBeq]
  | .empty, .target .. => by simp [heightPairBeq]
  | .empty, .emptyTarget _ => by simp [heightPairBeq]

/-- `finalityPairBeq` decides equality of finality pairs. -/
theorem finalityPairBeq_iff :
    ∀ (a b : FinalityPair Validator), finalityPairBeq a b = true ↔ a = b
  | .pair h T, .pair h' T' => by
      rw [finalityPairBeq, Bool.and_eq_true, blockBeq_iff T T']
      simp only [beq_iff_eq, FinalityPair.pair.injEq]
  | .empty, .empty => by simp [finalityPairBeq]
  | .pair .., .empty => by simp [finalityPairBeq]
  | .empty, .pair .. => by simp [finalityPairBeq]

end

instance : DecidableEq (Block Validator) := fun a b => decidable_of_iff _ (blockBeq_iff a b)

instance : DecidableEq (Attestation Validator) :=
  fun a b => decidable_of_iff _ (attBeq_iff a b)

instance : DecidableEq (HeightPair Validator) :=
  fun a b => decidable_of_iff _ (heightPairBeq_iff a b)

instance : DecidableEq (FinalityPair Validator) :=
  fun a b => decidable_of_iff _ (finalityPairBeq_iff a b)

end DecEq

namespace Block

/-- `B.parent`, `⊥` at genesis. -/
def parent : Block Validator → Option (Block Validator)
  | .genesis => ⊥
  | .mk p _ _ _ => some p

/-- `B.slot`. Genesis is at slot 0. -/
def slot : Block Validator → Nat
  | .genesis => 0
  | .mk _ s _ _ => s

/-- `B.attestations`. Empty at genesis. -/
def attestations : Block Validator → List (Attestation Validator)
  | .genesis => []
  | .mk _ _ as _ => as

/-- `B.proposal_root`, a block or `⊥`, read only in opening blocks. `⊥` at genesis, which
    the draft's "every other block" clause does not cover. -/
def proposalRoot : Block Validator → Option (Block Validator)
  | .genesis => ⊥
  | .mk _ _ _ pr => pr

end Block

/-! ## Ancestry -/

/-- The block and all of its ancestors, nearest first. Structural recursion on the parent
    link, so `⪯` needs no termination argument and no slot hypothesis. -/
def ancestors : Block Validator → List (Block Validator)
  | .genesis => [.genesis]
  | .mk p s as pr => .mk p s as pr :: ancestors p

/-- `B ⪯ C`: `B = C`, or `B` is an ancestor of `C`. The draft's reflexive ancestry, from
    Definition 1. -/
def Preceq (a b : Block Validator) : Prop := a ∈ ancestors b

@[inherit_doc] scoped infix:50 " ⪯ " => Preceq

instance [DecidableEq Validator] : DecidableRel (Preceq (Validator := Validator)) :=
  fun a b => inferInstanceAs (Decidable (a ∈ ancestors b))

end Consensus
