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
