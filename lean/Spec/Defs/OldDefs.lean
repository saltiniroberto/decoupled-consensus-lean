import Spec.Defs.Nondet
import Spec.Defs.Store

/-!
# Parked definitions: compiled, unconsumed

**This file is not a specification.** It holds machinery with no current consumer, kept
compiling here instead of deleted, so reviving a piece is a move into a spec file rather
than an excavation. Each entry says what it is and what would revive it. Nothing under
`Spec/` may import this file: a revived definition moves out first.
-/

set_option autoImplicit false

namespace DC

open Lean

/-- `σ.arr[i][j] ← e`, a two-level indexed write to a function-valued field, and
    `x[i][j] ← e` to a function-valued local. No two-level store map remains — the
    healing per-round bookkeeping it served is read off the SG votes now — so it has no
    consumer. Revived by any store field of shape `κ₁ → κ₂ → Option V`. One `macro`
    command, deliberately: declared as `syntax` plus a separate `macro_rules`, the
    pattern quotation is ambiguous with core's pattern-bind and the expansion never
    fires (measured). -/
scoped macro (name := idxAssign2) (priority := 1100)
    x:ident noWs "[" i:term "]" "[" j:term "]" " ← " e:term : doElem => do
  let n := x.getId
  let pre := n.getPrefix
  if pre.isAnonymous then
    `(doElem| $x:ident :=
        Function.update $x:ident $i (Function.update ($x:ident $i) $j $e))
  else
    let v := mkIdent pre
    let f := mkIdent (Name.mkSimple n.getString!)
    `(doElem| $v:ident :=
        { $v with $f:ident := (Function.update (($v).$f:ident) $i
            (Function.update ((($v).$f:ident) $i) $j $e)) })

/-- `times[x]`, the raising read on a `TimeMap`: when `x` was processed, or the
    failure. Its readers went when the stored votes began carrying their own times
    (`TimestampedVote`), and the one remaining `TimeMap` — the blocks' — is read by
    nothing. Revived by any rule that reads a `TimeMap` with the protocol's bracket. -/
scoped instance timeMapGetElem {α : Type} :
    GetElem (TimeMap α) α (DRE Int) (fun _ _ => True) where
  getElem times x _ := if h : (times x).isSome then .ok ((times x).get h) else .error .error

/-- `d.withSend prior`: a `DutyResult` with an earlier duty's broadcasts unioned into
    its own. In the duty monad the outbox carries earlier sends, so nothing unions.
    Revived by any composition done on `DutyResult` values rather than in the monad. -/
def DutyResult.withSend {Validator : Type} [Roots] [DecidableEq Validator]
    (d : DutyResult Validator) (prior : Finset (Message Validator)) :
    DutyResult Validator :=
  { d with send := prior ∪ d.send }

end DC
