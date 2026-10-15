# What the library `Spec` imports

The library imports Mathlib and its own files, nothing else. `lean/Sts.lean`, which places the
node under the sts framework, imports the library and the framework. No file of `Spec` imports a
module of `Model` or `Proofs`.

This page was measured from the `import` lines of the files, and from the `open` lines and the
names each file uses.

## Every import

| file | imports |
| --- | --- |
| `lean/Spec.lean` | the fifteen files of the library outside `lean/Spec/Defs/`, listed in this table |
| `lean/Spec/Objects.lean` | `Mathlib.Algebra.BigOperators.Group.Finset.Basic`, `Mathlib.Algebra.Order.Group.Int`, `Mathlib.Data.Fintype.Basic`, `Mathlib.Data.Prod.Lex`, `Mathlib.Order.WithBot`, `Spec.Defs.Notation` |
| `lean/Spec/Config.lean` | `Spec.Objects` |
| `lean/Spec/Protocol/ChainState.lean` | `Spec.Config`, `Spec.Objects`, `Spec.Defs.Notation` |
| `lean/Spec/Store.lean` | `Spec.Defs.Notation`, `Spec.Config`, `Spec.Objects`, `Spec.Protocol.ChainState` |
| `lean/Spec/Protocol/ValidatorClient.lean` | `Spec.Defs.Notation`, `Spec.Defs.Raise`, `Spec.Store` |
| `lean/Spec/NodeState.lean` | `Spec.Store`, `Spec.Protocol.ValidatorClient`, `Spec.Defs.Raise` |
| `lean/Spec/Broadcast.lean` | `Spec.Objects`, `Spec.Defs.Raise` |
| `lean/Spec/Protocol/ForkChoice/Goldfish.lean` | `Spec.Store` |
| `lean/Spec/Protocol/ForkChoice/Views.lean` | `Spec.Store`, `Spec.Defs.Notation` |
| `lean/Spec/Protocol/ForkChoice/Head.lean` | `Spec.Protocol.ForkChoice.Goldfish` |
| `lean/Spec/Protocol/Grades.lean` | `Spec.Protocol.ForkChoice.Head`, `Spec.Defs.Notation` |
| `lean/Spec/Protocol/GoldfishVotes.lean` | `Spec.Protocol.ForkChoice.Views`, `Spec.Protocol.ForkChoice.Head`, `Spec.Protocol.Grades`, `Spec.Broadcast`, `Spec.Defs.Notation` |
| `lean/Spec/Protocol/Attestations.lean` | `Spec.Protocol.ForkChoice.Views`, `Spec.Protocol.ForkChoice.Head`, `Spec.Protocol.Grades`, `Spec.Protocol.ValidatorClient`, `Spec.Broadcast`, `Spec.Defs.Notation` |
| `lean/Spec/Protocol/Blocks.lean` | `Spec.Protocol.ForkChoice.Views`, `Spec.Protocol.ForkChoice.Head`, `Spec.Protocol.Grades`, `Spec.Protocol.GoldfishVotes`, `Spec.Protocol.Attestations`, `Spec.Broadcast`, `Mathlib.Data.Finset.Sort`, `Spec.Defs.Notation` |
| `lean/Spec/Node.lean` | `Spec.NodeState`, `Spec.Protocol.GoldfishVotes`, `Spec.Protocol.Attestations`, `Spec.Protocol.Blocks`, `Spec.Defs.Notation` |
| `lean/Spec/Defs/FinsetM.lean` | `Mathlib.Data.Finset.Fold` |
| `lean/Spec/Defs/Model.lean` | `Mathlib.Algebra.BigOperators.Group.Finset.Defs`, `Mathlib.Data.Finset.Card`, `Mathlib.Data.Finset.Max`, `Mathlib.Data.Finset.Lattice.Basic` |
| `lean/Spec/Defs/Raise.lean` | `Spec.Defs.Model`, `Spec.Defs.FinsetM` |
| `lean/Spec/Defs/Notation.lean` | `Spec.Defs.Model`, `Spec.Defs.FinsetM`, `Spec.Defs.Raise` |
| `lean/Spec/Defs/Nondet.lean` | `Mathlib.Data.Set.Functor`, `Spec.Defs.Raise` |
| `lean/Sts.lean` | `Spec`, `StsMultisetLog` (the framework of `deps/lean-sts`) |

So the Mathlib modules the library imports directly are the five of `lean/Spec/Objects.lean`,
`Mathlib.Data.Finset.Sort` (for the sorted list of block roots, `lean/Spec/Protocol/Blocks.lean`),
and the six imported by `lean/Spec/Defs/`.

## What `lean/Spec/Defs/` provides

The five files hold no protocol content. Four of them declare in the namespace `DC`, and most of
what they declare is `scoped`: it is active only in a file that writes `open scoped DC`. Twelve
of the fifteen routine files write it; `lean/Spec/Config.lean`, `lean/Spec/Broadcast.lean` and
`lean/Spec/Protocol/ForkChoice/Head.lean` do not. Ten of them also write `open DC (DRE)`, which
makes the name `DRE` available without its namespace.

**`lean/Spec/Defs/Raise.lean`: failure.**

- `DC.Error`, one failure value that carries nothing (`lean/Spec/Defs/Raise.lean:49`), and the
  instance that any two failures are equal (`lean/Spec/Defs/Raise.lean:55`);
- `DC.DRE α`, the result type of a routine that can fail: `Except Error α`
  (`lean/Spec/Defs/Raise.lean:65`);
- `Option.value`, the read of an optional value `x`, which takes a proof that `x` is not empty as
  an argument that is not written (`lean/Spec/Defs/Raise.lean:75`);
- the instances that `Finset.unionM` at `DRE` is commutative and associative, which
  `Finset.filterM` needs (`lean/Spec/Defs/Raise.lean:82`, `lean/Spec/Defs/Raise.lean:93`);
- a scoped lift, by which `let y ← x` reads an optional value `x` in a routine that can fail, and
  fails when `x` is empty (`lean/Spec/Defs/Raise.lean:112`).

**`lean/Spec/Defs/FinsetM.lean`: monadic operations on finite sets**, in the namespace `Finset`.

- `Finset.unionM`, run two computations of sets and take the union
  (`lean/Spec/Defs/FinsetM.lean:39`);
- `Finset.filterM`, keep the members a test accepts when the test can fail
  (`lean/Spec/Defs/FinsetM.lean:46`);
- `Finset.map'`, Mathlib's `Finset.image` under another name, which the image comprehension of
  `lean/Spec/Defs/Notation.lean` expands to (`lean/Spec/Defs/FinsetM.lean:56`).

**`lean/Spec/Defs/Notation.lean`: the notation of the routines**, all scoped in `DC`.

- the assignment arrow `x ← e` and `σ.f ← e`, for a plain value (`lean/Spec/Defs/Notation.lean:77`);
- the simultaneous assignment `σ.f, σ.g ← e` (`lean/Spec/Defs/Notation.lean:93`);
- the indexed write `σ.f[i] ← e` to a field that holds a function (`lean/Spec/Defs/Notation.lean:104`);
- the arrow `x ⇐ e`, whose right-hand side is a computation that may fail or send
  (`lean/Spec/Defs/Notation.lean:122`);
- the destructuring assignment `let {f := x, g ← y} := e`, and its form with `⇐`
  (`lean/Spec/Defs/Notation.lean:169`, `lean/Spec/Defs/Notation.lean:174`);
- the raising set-builder `let y ← {x ∈ᴹ s | p}`, a filter whose condition may fail
  (`lean/Spec/Defs/Notation.lean:223`);
- the image comprehension `{f x | x ∈ s}` and `{f x | x ∈ s, p x}`
  (`lean/Spec/Defs/Notation.lean:236`, `lean/Spec/Defs/Notation.lean:240`);
- `|s|` for the size of a finite set (`lean/Spec/Defs/Notation.lean:256`).

**`lean/Spec/Defs/Model.lean`: the `⊥` of an optional value.** Its one declaration is the scoped
instance that writes the empty optional value `none` as `⊥` (`lean/Spec/Defs/Model.lean:61`),
read through `Option.value`, whose unwritten argument has the type `x ≠ ⊥`. It is imported because
`Raise.lean` and `Notation.lean` import it. Its section `## Extract` is the opening prose of the
generated document.

**`lean/Spec/Defs/Nondet.lean`: the result types of a routine that picks.** `DC.NDR α` and
`DC.NDRE α` (`lean/Spec/Defs/Nondet.lean:46`, `lean/Spec/Defs/Nondet.lean:50`). No file of the library
imports it, and no routine of the library picks. It belongs to the library because the library's
glob in `lakefile.toml` takes every module under `lean/Spec/`; the module that imports it is
`lean/Model/Record/Model.lean`, the record of `PROVING.md`.

## The notation the library declares itself

Four pieces of notation are declared outside `lean/Spec/Defs/`, scoped in the namespace `Spec`:

- an `if` whose condition mentions `none`, `⊥` or `pending` hands the fact of its condition to its
  branches, so that `x.value` is accepted under `if x ≠ none then` (`lean/Spec/Objects.lean:103`);
- the assignment arrow on a path of two fields or more, `st.saved_grades.next.g2 ← e`
  (`lean/Spec/Objects.lean:120`);
- `p <[lex] q`, the lexicographic order on pairs (`lean/Spec/Objects.lean:132`);
- the brackets `f[a]`, which read a field that holds a function as `f a`
  (`lean/Spec/Store.lean:180`).

`STYLE.md` says how each is used.
