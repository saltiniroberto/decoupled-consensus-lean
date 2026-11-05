module
public import GoldilocksCorrectness.Statements.View.NodeViewDefs

@[expose] public section

/-!
# The network premises read the same on a projected trace

The premises of `Statements/Network/NetworkDefs.lean` read a trace's times, labels and sent log, and
never a node state; `projectTrace f` keeps all three. So each premise holds of `projectTrace f x`
exactly when it holds of `x`, and a statement may state its premises on the trace of views as well
as on the execution's trace. Each equivalence is `Iff.rfl`, except `Unforgeability`, a structure,
whose two fields carry over unchanged.

The same holds of the readers `HonestThroughV` and `PutsBlockV`.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Proofs.View

open Framework.StsMultisetLog (Schedule SignedMsg)
open GoldilocksCorrectness.Statements.Network
open GoldilocksCorrectness.Statements.View

variable {Node Msg St St' Ev : Type} (f : (n : St) → St') (x : Trace Node Msg St Ev)

/-- Every time is reached by `projectTrace f x` exactly when every time is reached by `x`.

Read aloud: the projection keeps the times. -/
theorem timeDiverges_projectTrace : TimeDiverges (projectTrace f x) ↔ TimeDiverges x := Iff.rfl

/-- `v` is honest through step `i` of `projectTrace f x` exactly when it is through step `i` of
`x`.

Read aloud: the projection keeps the time of every step, so honesty through a step is unchanged. -/
theorem honestThroughV_projectTrace (Sched : Schedule Node) (i : ℕ) (v : Node) :
    HonestThroughV Sched (projectTrace f x) i v ↔ HonestThroughV Sched x i v := Iff.rfl

section Delivery

variable [DecidableEq Node] [DecidableEq Msg] [Fintype Node] (Sched : Schedule Node)

omit [Fintype Node] in
/-- A step of `projectTrace f x` puts a message an honest validator signed on the wire exactly
when that step of `x` does.

Read aloud: the projection keeps every send. -/
theorem honestSendAt_projectTrace (i : ℕ) (sm : SignedMsg Node Msg) :
    HonestSendAt Sched (projectTrace f x) i sm ↔ HonestSendAt Sched x i sm := Iff.rfl

/-- Synchrony from the receiver's wake holds of `projectTrace f x` exactly when it holds of `x`.

Read aloud: the projection keeps every send and every delivery. -/
theorem synchronyFromWake_projectTrace (Δ GST : ℕ) (ok : (m : Msg) → Prop) :
    SynchronyFromWake Sched (projectTrace f x) Δ GST ok ↔ SynchronyFromWake Sched x Δ GST ok :=
  Iff.rfl

/-- Catch-up on wake holds of `projectTrace f x` exactly when it holds of `x`.

Read aloud: the projection keeps every send and every delivery. -/
theorem catchUpOnWake_projectTrace (Δ GST : ℕ) (ok : (m : Msg) → Prop) :
    CatchUpOnWake Sched (projectTrace f x) Δ GST ok ↔ CatchUpOnWake Sched x Δ GST ok :=
  Iff.rfl

/-- Synchrony suspended on the asynchronous period `[b₀, b₁)` holds of `projectTrace f x` exactly
when it holds of `x`.

Read aloud: the projection keeps every send and every delivery. -/
theorem synchronyFromWakeOutside_projectTrace (Δ GST : ℕ) (ok : (m : Msg) → Prop) (b₀ b₁ : ℕ) :
    SynchronyFromWakeOutside Sched (projectTrace f x) Δ GST ok b₀ b₁ ↔
      SynchronyFromWakeOutside Sched x Δ GST ok b₀ b₁ := Iff.rfl

/-- Catch-up on wake suspended on the asynchronous period `[b₀, b₁)` holds of `projectTrace f x`
exactly when it holds of `x`.

Read aloud: the projection keeps every send and every delivery. -/
theorem catchUpOnWakeOutside_projectTrace (Δ GST : ℕ) (ok : (m : Msg) → Prop) (b₀ b₁ : ℕ) :
    CatchUpOnWakeOutside Sched (projectTrace f x) Δ GST ok b₀ b₁ ↔
      CatchUpOnWakeOutside Sched x Δ GST ok b₀ b₁ := Iff.rfl

omit [DecidableEq Node] [DecidableEq Msg] [Fintype Node] in
/-- Unforgeability holds of `projectTrace f x` exactly when it holds of `x`.

Read aloud: the projection keeps every message on the wire and every time. -/
theorem unforgeability_projectTrace {B : Type} (W : ViewVocab Node B Msg) :
    Unforgeability W Sched (projectTrace f x) ↔ Unforgeability W Sched x :=
  ⟨fun h => ⟨h.unforgeable, h.carried⟩, fun h => ⟨h.unforgeable, h.carried⟩⟩

omit [Fintype Node] in
/-- `v` puts the block `b` on the wire at step `i` of `projectTrace f x` exactly when it does at
step `i` of `x`.

Read aloud: the projection keeps every block sent. -/
theorem putsBlockV_projectTrace {B : Type} (W : ViewVocab Node B Msg) (i : ℕ) (v : Node) (b : B) :
    PutsBlockV W (projectTrace f x) i v b ↔ PutsBlockV W x i v b := Iff.rfl

end Delivery

end GoldilocksCorrectness.Proofs.View
