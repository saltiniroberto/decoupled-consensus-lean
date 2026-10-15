module
public import Model.Sts.Spec2Claims.Claim13bf
public import Proofs.Claims.Spec2Claims.Claim13bSGCompatible

@[expose] public section

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-!
# The delivery deadline around an asynchronous period

The deadline `deadlineOutside` a send keeps around one asynchronous period `[b₀, b₁)`.
-/

/-- The delivery deadline around one asynchronous period `[b₀, b₁)`: a send at instant `t` whose
    ordinary deadline `max t S.E.t_GST + S.E.Δ` is at or before `b₀` keeps it; any other send gets
    `Δ` after the latest of `t`, `b₁` and `S.E.t_GST`. -/
def deadlineOutside (S : Setup V) (b₀ b₁ : Int) (t : Int) : Int :=
  if max t S.E.t_GST + S.E.Δ ≤ b₀ then max t S.E.t_GST + S.E.Δ
  else max t (max b₁ S.E.t_GST) + S.E.Δ

end

end DecoupledConsensusModel.Sts
