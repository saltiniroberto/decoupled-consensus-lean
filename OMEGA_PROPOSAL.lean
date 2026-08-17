import Spec.HftFig2Store

/-!
# Proposal: `get_confirmed` as a deterministic function, `Ω` ambient

**Temporary file, untracked, imported by nothing** — it compiles against the library
(`lake env lean OMEGA_PROPOSAL.lean` from the repository root) but is not part of the
build, so it disturbs no running job. Delete it, or move its pieces into place, once the
design is agreed.

The design decided so far (2026-08-17): `Ω` stays **out of the store** — Definition 10
(`hft:def:store`) lists six components and the paper deliberately treats `Ω` as call-time
input — and out of explicit signatures. The device is a typeclass, the same way
`BlockHash` keeps `hash(·)` ambient.

Three pieces:

* `getConfirmedSet` — the candidate set, computable. Nondeterminism as a function is the
  set of admissible outcomes; `mem_getConfirmedSet` proves it is exactly the relation
  `GetConfirmed`, so the statements of record are untouched by adopting this.
* `Omega` — the selection the paper leaves open. An instance is one selection rule,
  ambient for the whole context; a theorem binding `[Omega Node Root]` quantifies over
  every rule, which is the paper's "for every Ω". For per-validator rules the field would
  take the validator too (`choose : Node → (s : Finset _) → …`); the paper's per-call-site
  variation is not expressible with a fixed instance, and that is the accepted cost.
* `getConfirmed` — the paper's `get_confirmed(Σ, Ω)` with `Ω` invisible. The nonemptiness
  argument is Corollary 1's obligation (`hft:cor:getConfirmed-total`): for an arbitrary
  store the candidate set can be empty; discharging it for held stores needs
  `S.F ∈ viableTree S`, the paper's Lemma 7, not yet proved. An `Option`-returning
  variant would avoid the argument at the cost of an `Option` at every use.

If adopted: `getConfirmedSet` and `mem_getConfirmedSet` beside `GetConfirmed` in
`Spec/HftFig2Store.lean`; `Omega` beside `BlockHash` in `Spec/Defs/Store.lean`;
`getConfirmed` with them. Nothing existing changes.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled

variable {Node Root : Type}

section
variable [DecidableEq Node] [DecidableEq Root]

/-- The candidate set of `get_confirmed` (Figure 2, `hft:alg:store`, line 561): the blocks
    some `Ω` could pick. Computable; `mem_getConfirmedSet` says membership is exactly the
    relation `GetConfirmed`. -/
def getConfirmedSet (S : Store Node Root) : Finset (Blk Node Root) :=
  (viableTree S).filter fun B => S.R ⪯ B ∧ (S.σ B).any fun st => st.h ≥ S.hmax - 1

/-- The candidate set is the relation: adopting the function view changes no statement. -/
theorem mem_getConfirmedSet {S : Store Node Root} {B : Blk Node Root} :
    B ∈ getConfirmedSet S ↔ GetConfirmed S B := by
  unfold getConfirmedSet GetConfirmed
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    cases hσ : S.σ B with
    | none => rw [hσ] at h3; exact absurd h3 (by simp)
    | some st =>
        rw [hσ] at h3
        exact ⟨st, rfl, by simpa using h3⟩
  · rintro ⟨h1, h2, st, hst, h3⟩
    have hst' : S.σ B = some st := hst
    refine ⟨h1, h2, ?_⟩
    rw [hst']
    simp
    omega

/-- The selection the paper writes as `Ω` — "whatever extra information the validator uses
    to disambiguate among viable descendants of the walk-from block". An instance is one
    selection rule; binding `[Omega Node Root]` quantifies over all of them. Ambient by
    typeclass, as `BlockHash` is. -/
class Omega (Node Root : Type) where
  /-- Pick a block from a nonempty candidate set. The subtype carries the membership
      proof, so anything picked satisfies `GetConfirmed`. -/
  choose : (s : Finset (Blk Node Root)) → s.Nonempty → {B // B ∈ s}

/-- `get_confirmed(Σ, Ω)` as a deterministic function of the store, `Ω` ambient. The
    nonemptiness argument is Corollary 1's obligation — see the module header. -/
def getConfirmed [Omega Node Root] (S : Store Node Root)
    (h : (getConfirmedSet S).Nonempty) : Blk Node Root :=
  (Omega.choose (getConfirmedSet S) h).val

/-- Whatever the function returns, the relation admits: every statement over
    `GetConfirmed` applies to the function's output unchanged. -/
theorem getConfirmed_spec [Omega Node Root] (S : Store Node Root)
    (h : (getConfirmedSet S).Nonempty) :
    GetConfirmed S (getConfirmed S h) :=
  mem_getConfirmedSet.mp (Omega.choose (getConfirmedSet S) h).property

end

end Decoupled
