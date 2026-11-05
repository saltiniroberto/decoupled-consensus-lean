module
public import Goldilocks.Objects
public import Spec2.Defs.Raise

@[expose] public section

/-!
# The duty monad, `DREB`, and `broadcast`

A duty that sends objects does not return them. It calls `broadcast` on each object it sends, and
returns only what it changes. The objects sent are kept by the monad the duty runs in, `DREB V`,
in the order they were sent. A routine that calls two such duties one after the other does not
join their lists: the objects the first sent are already in the list when the second runs.

This file declares, in the namespace `Goldilocks`:

- `DREB V α`: the result type of a duty that sends objects. It is `StateT` of a list of objects
  (`NamedObject V`, a block, a Goldfish vote or an attestation, declared in
  `Goldilocks/Objects.lean`) over `DRE`, the deterministic result or the failure. So, under the
  `abbrev`, a value of `DREB V α` is a function that takes the list of objects sent so far and
  returns either the failure, or an answer of type `α` paired with the list of objects sent so far
  after it.
- `broadcast m`: append the object `m` to that list.

**Calling a routine of `DRE` inside `DREB`.** A routine whose result type is `DRE α` is called
inside a `do` block of `DREB V` with `←` and no extra word: Lean's instance
`StateT.instMonadLift` lifts it, so it raises where it raises and sends nothing.

**Reading a duty from outside.** A caller that is not itself a duty runs it from the empty list:
`d.run []` has the type `DRE (α × List (NamedObject V))`; it is the failure, or the duty's answer
paired with the list of the objects the duty sent, in the order sent.

This file holds definitions only.
-/

open DC (DRE)

namespace Goldilocks

/-- The result type of a duty that sends objects: `StateT` of the list of the objects sent so far
(`NamedObject V`) over `DRE`. A value of `DREB V α` takes the list of the objects sent before it
runs, and returns either the failure, or an answer of type `α` paired with that list followed by
the objects it sent, in the order sent. -/
abbrev DREB (V : Type) (α : Type) :=
  StateT (List (NamedObject V)) DRE α

/-- Send the object `m`: append `m` to the list of the objects sent so far. -/
def broadcast {V : Type} (m : NamedObject V) : DREB V Unit :=
  modify (· ++ [m])

/-- `d.outcomes`: the set of outcomes of the duty `d` run with nothing sent. Each element is the
failure, or an answer paired with the list of the objects the duty sent. For the deterministic
duty monad `DREB` this is the one-element set `{d.run []}`; the type is the one a nondeterministic
duty monad has too, so a statement over `d.outcomes` survives a spec change that adds picks.

Read aloud: everything the duty may do when run from scratch. -/
def DREB.outcomes {V α : Type} (d : DREB V α) :
    Set (DRE (α × List (NamedObject V))) :=
  {d.run []}

end Goldilocks
